-- Prove2me | solution 1 for InfFisher.QL.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T11:49:17.405611+00:00
-- url     : https://prove2.me/submissions/dd2f1464-2dd1-4a75-9927-6d1aaf40871d

import Mathlib
import Definitions.Def_InfFisher_EG_Market
import Definitions.Def_InfFisher_QL_Setting

open InfFisher.QL
open MeasureTheory

theorem solution
    {d n : ℕ} (Θ : Set (EuclideanSpace ℝ (Fin d))) (hΘ : IsCompact Θ)
    (v : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (hv : ∀ i, Integrable (v i) (volume.restrict Θ))
    (hv0 : ∀ i, 0 ≤ᵐ[volume.restrict Θ] v i)
    (hvpos : ∀ i, 0 < ∫ θ in Θ, v i θ)
    (B : Fin n → ℝ) (hB : ∀ i, 0 < B i)
  :
    let μ : Measure (EuclideanSpace ℝ (Fin d)) := volume.restrict Θ
    ∀ (x : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
      (u δ : Fin n → ℝ), InfFisher.EG.IsAllocation μ x →
      (∀ i, 0 < u i) → (∀ i, 0 ≤ δ i) →
      (∀ i, u i ≤ InfFisher.EG.pair μ (v i) (x i) + δ i) →
      ∀ p β, IsDQLFeasible μ v p β → (∀ i, 0 < β i) →
        (∑ i, (B i * Real.log (u i) - δ i)) ≤
          InfFisher.EG.degObj μ B p β + ∑ i, B i * (Real.log (B i) - 1) := by
  intro μ x u δ hx hu hδ hux p β hpβ hβ
  obtain ⟨⟨⟨hpI, hp0⟩, hβ0, hle⟩, hβ1⟩ := hpβ
  have hpx : ∀ i, Integrable (fun θ => p θ * x i θ) μ := fun i => hpI.mul_of_top_left (hx.1 i).1
  have hvx : ∀ i, Integrable (fun θ => v i θ * x i θ) μ := fun i => (hv i).mul_of_top_left (hx.1 i).1
  have step3 : ∀ i, β i * InfFisher.EG.pair μ (v i) (x i) ≤ InfFisher.EG.pair μ p (x i) := by
    intro i
    unfold InfFisher.EG.pair
    rw [← integral_const_mul]
    apply integral_mono_ae ((hvx i).const_mul (β i)) (hpx i)
    filter_upwards [hle i, (hx.1 i).2] with θ h1 h2
    have h2' : 0 ≤ x i θ := h2
    have h1' : β i * v i θ ≤ p θ := h1
    nlinarith
  have step4 : ∑ i, InfFisher.EG.pair μ p (x i) ≤ ∫ θ, p θ ∂μ := by
    unfold InfFisher.EG.pair
    rw [← integral_finsetSum _ (fun i _ => hpx i)]
    apply integral_mono_ae (integrable_finsetSum _ (fun i _ => hpx i)) hpI
    filter_upwards [hx.2, hp0] with θ h1 h2
    have h2' : 0 ≤ p θ := h2
    rw [← Finset.mul_sum]
    nlinarith
  have step1 : ∀ i, B i * Real.log (u i) - δ i ≤
      B i * Real.log (B i) - B i - B i * Real.log (β i) + InfFisher.EG.pair μ p (x i) := by
    intro i
    have hb := hB i
    have hl := Real.log_le_sub_one_of_pos (show 0 < β i * u i / B i by
      have := hβ i; have := hu i; positivity)
    rw [Real.log_div (by have := hβ i; have := hu i; positivity) hb.ne',
      Real.log_mul (hβ i).ne' (hu i).ne'] at hl
    have h1 : B i * (Real.log (β i) + Real.log (u i) - Real.log (B i)) ≤
        B i * (β i * u i / B i - 1) := mul_le_mul_of_nonneg_left hl hb.le
    have h2 : B i * (β i * u i / B i - 1) = β i * u i - B i := by field_simp
    have h3 : β i * u i ≤ β i * InfFisher.EG.pair μ (v i) (x i) + δ i := by
      have := mul_le_mul_of_nonneg_left (hux i) (hβ0 i)
      nlinarith [hδ i, hβ1 i]
    have h4 := step3 i
    nlinarith
  unfold InfFisher.EG.degObj
  calc ∑ i, (B i * Real.log (u i) - δ i)
      ≤ ∑ i, (B i * Real.log (B i) - B i - B i * Real.log (β i) + InfFisher.EG.pair μ p (x i)) :=
        Finset.sum_le_sum (fun i _ => step1 i)
    _ = ∑ i, InfFisher.EG.pair μ p (x i) - ∑ i, B i * Real.log (β i)
          + ∑ i, B i * (Real.log (B i) - 1) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        ring
    _ ≤ _ := by linarith

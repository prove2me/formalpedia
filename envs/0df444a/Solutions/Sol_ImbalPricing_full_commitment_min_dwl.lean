-- Prove2me | solution 1 for ImbalPricing.full_commitment_min_dwl
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T17:21:09.76462+00:00
-- url     : https://prove2.me/submissions/f60f61c9-13ea-496d-bae1-33cece61d88e

import Mathlib
import Definitions.Def_ImbalPricing_Market
import Definitions.Def_ImbalPricing_ExpectedDWL

open MeasureTheory

namespace Aux_ImbalPricing_fc
open ImbalPricing

lemma int1 (a b α : ℝ) : ∫ h in a..b, α * h = α * (b ^ 2 - a ^ 2) / 2 := by
  rw [intervalIntegral.integral_const_mul, integral_id]; ring

lemma int2 (H b α₁ α₂ : ℝ) :
    ∫ h in H..b, (α₁ * H + α₂ * (h - H)) = α₁ * H * (b - H) + α₂ * (b - H) ^ 2 / 2 := by
  have e : (fun h : ℝ => α₁ * H + α₂ * (h - H)) = fun h => (α₁ * H - α₂ * H) + α₂ * h := by
    funext h; ring
  rw [e, intervalIntegral.integral_add (f := fun _ => α₁ * H - α₂ * H) (g := fun h => α₂ * h)
    intervalIntegrable_const ((continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, integral_id,
    smul_eq_mul]
  ring

lemma dwl_eq (α₁ α₂ H₁ H₂ : ℝ) : dwl α₁ α₂ H₁ H₂ = (α₂ - α₁) / 2 * H₂ ^ 2 := by
  unfold dwl hcgCost
  rw [int1, int1, int2, int2]
  ring

end Aux_ImbalPricing_fc

open ImbalPricing Aux_ImbalPricing_fc in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (M : Market Ω N)
    (hM : M.Standing) (d : Fin N → ℝ) :
    M.expectedDWL 0 ≤ M.expectedDWL d := by
  haveI := hM.isProb
  set Z : Ω → ℝ := fun ω => M.ε ω - ∑ i, M.γ i * M.ν i ω with hZ
  have hH2 : ∀ (d : Fin N → ℝ) ω, M.H2 d ω = Z ω + ∑ i, M.γ i * d i := by
    intro d ω
    simp only [Market.H2, Market.L2, Market.L2i, hZ, mul_sub, Finset.sum_sub_distrib]
    ring
  have hZm : MemLp Z 2 M.μ := by
    refine hM.ε_memLp.sub ?_
    exact memLp_finsetSum _ (fun i _ => (hM.ν_memLp i).const_mul (M.γ i))
  have hZi : Integrable Z M.μ := hZm.integrable one_le_two
  have hZ2 : Integrable (fun ω => Z ω ^ 2) M.μ := hZm.integrable_sq
  have hZ0 : ∫ ω, Z ω ∂M.μ = 0 := by
    simp only [hZ]
    rw [integral_sub (hM.ε_memLp.integrable one_le_two)
      (integrable_finsetSum _ (fun i _ => ((hM.ν_memLp i).integrable one_le_two).const_mul _)),
      integral_finsetSum _ (fun i _ => ((hM.ν_memLp i).integrable one_le_two).const_mul _),
      hM.ε_mean]
    simp only [integral_const_mul, hM.ν_mean, mul_zero, Finset.sum_const_zero, sub_zero]
  have key : ∀ d : Fin N → ℝ, M.expectedDWL d
      = (M.α₂ - M.α₁) / 2 * (∫ ω, Z ω ^ 2 ∂M.μ + (∑ i, M.γ i * d i) ^ 2) := by
    intro d
    set c := ∑ i, M.γ i * d i with hc
    unfold Market.expectedDWL Market.DWL
    have e : ∀ ω, dwl M.α₁ M.α₂ (M.H1 d) (M.H2 d ω)
        = (M.α₂ - M.α₁) / 2 * (Z ω ^ 2 + (2 * c) * Z ω + c ^ 2) := by
      intro ω; rw [dwl_eq, hH2]; ring
    simp only [e]
    have i1 : Integrable (fun ω => Z ω ^ 2 + 2 * c * Z ω) M.μ := hZ2.add (hZi.const_mul _)
    have i2 : Integrable (fun ω => 2 * c * Z ω) M.μ := hZi.const_mul _
    rw [integral_const_mul, integral_add i1 (integrable_const _), integral_add hZ2 i2,
      integral_const_mul, hZ0, integral_const]
    simp only [probReal_univ, smul_eq_mul, one_mul, mul_zero, add_zero]
  rw [key, key]
  have hα : 0 ≤ (M.α₂ - M.α₁) / 2 := by linarith [hM.α₁_le_α₂]
  apply mul_le_mul_of_nonneg_left _ hα
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  nlinarith [sq_nonneg (∑ i, M.γ i * d i)]

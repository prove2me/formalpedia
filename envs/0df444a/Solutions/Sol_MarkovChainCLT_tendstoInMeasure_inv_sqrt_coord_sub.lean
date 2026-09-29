-- Prove2me | solution 1 for MarkovChainCLT.tendstoInMeasure_inv_sqrt_coord_sub
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T18:09:45.037981+00:00
-- url     : https://prove2.me/submissions/59a38c2e-16fc-43f6-a91f-2e7094e50367

import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure

set_option maxHeartbeats 1000000

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (h : X → ℝ) (hhm : Measurable h) (hh : Integrable h π) :
    TendstoInMeasure (chainMeasure P π)
      (fun (n : ℕ) (ω : ℕ → X) => (Real.sqrt n)⁻¹ * (h (ω 0) - h (ω n))) atTop 0 := by
  set μ := chainMeasure P π with hμ
  -- every coordinate has law π, so `h ∘ (· k)` has the same L¹ seminorm as `h`
  have hcoordL1 : ∀ k : ℕ, eLpNorm (fun ω : ℕ → X => h (ω k)) 1 μ = eLpNorm h 1 π := by
    intro k
    have hmap := map_coord_chainMeasure P π hP.1 k
    have hae : AEMeasurable (fun ω : ℕ → X => ω k) μ := (measurable_pi_apply k).aemeasurable
    have := eLpNorm_map_measure (p := 1) (μ := μ) (g := h)
      (by rw [hmap]; exact hhm.aestronglyMeasurable) hae
    rw [hmap] at this
    exact this.symm
  have hCfin : eLpNorm h 1 π ≠ ∞ := by
    rw [← memLp_one_iff_integrable] at hh
    exact hh.2.ne
  -- the L¹ seminorm of the boundary term is bounded uniformly in `n`
  have hbnd : ∀ n : ℕ, eLpNorm (fun ω : ℕ → X => h (ω 0) - h (ω n)) 1 μ
      ≤ 2 * eLpNorm h 1 π := by
    intro n
    have hm0 : AEStronglyMeasurable (fun ω : ℕ → X => h (ω 0)) μ :=
      (hhm.comp (measurable_pi_apply 0)).aestronglyMeasurable
    have hmn : AEStronglyMeasurable (fun ω : ℕ → X => h (ω n)) μ :=
      (hhm.comp (measurable_pi_apply n)).aestronglyMeasurable
    calc eLpNorm (fun ω : ℕ → X => h (ω 0) - h (ω n)) 1 μ
        ≤ eLpNorm (fun ω : ℕ → X => h (ω 0)) 1 μ
            + eLpNorm (fun ω : ℕ → X => h (ω n)) 1 μ := eLpNorm_sub_le hm0 hmn le_rfl
      _ = 2 * eLpNorm h 1 π := by rw [hcoordL1 0, hcoordL1 n]; ring
  -- hence the scaled boundary term tends to 0 in L¹
  refine tendstoInMeasure_of_tendsto_eLpNorm_of_ne_top (p := 1) one_ne_zero (by simp)
    (fun n => (((hhm.comp (measurable_pi_apply 0)).sub
      (hhm.comp (measurable_pi_apply n))).const_mul _).aestronglyMeasurable)
    aestronglyMeasurable_zero ?_
  have hkey : ∀ n : ℕ,
      eLpNorm ((fun (ω : ℕ → X) => (Real.sqrt n)⁻¹ * (h (ω 0) - h (ω n))) - 0) 1 μ
        ≤ ENNReal.ofReal ((Real.sqrt n)⁻¹) * (2 * eLpNorm h 1 π) := by
    intro n
    have hsm : ((fun (ω : ℕ → X) => (Real.sqrt n)⁻¹ * (h (ω 0) - h (ω n))) - 0)
        = (Real.sqrt n)⁻¹ • (fun ω : ℕ → X => h (ω 0) - h (ω n)) := by
      funext ω; simp [smul_eq_mul]
    rw [hsm]
    refine le_trans eLpNorm_const_smul_le ?_
    gcongr
    · simp [Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.sqrt n)⁻¹)]
    · exact hbnd n
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
    (fun n => by simp) hkey
  have h0 : Tendsto (fun n : ℕ => ENNReal.ofReal ((Real.sqrt n)⁻¹)) atTop (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    exact (ENNReal.continuous_ofReal.tendsto 0).comp
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop))
  simpa using ENNReal.Tendsto.mul_const h0 (Or.inr (ENNReal.mul_ne_top (by simp) hCfin))

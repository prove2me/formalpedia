-- Prove2me | solution 1 for MarkovChainCLT.clt_of_geometric_reversible
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T15:52:05.917613+00:00
-- url     : https://prove2.me/submissions/f35d8b90-1831-4240-86cb-d021c3d2d36e

import Theorems.Thm_MarkovChainCLT_rhoMixingCoef_comp_nonneg_le_of_finite
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_comp_of_measurable
import Theorems.Thm_MarkovChainCLT_isStrictlyStationary_coord_chainMeasure
import Theorems.Thm_MarkovChainCLT_map_coord_chainMeasure
import Theorems.Thm_MarkovChainCLT_satisfiesCLT_of_centered_functional_clt
import Theorems.Thm_MarkovChainCLT_clt_of_summable_rho
import Theorems.Thm_MarkovChainCLT_rho_mixing_exp_of_geometric_reversible

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hP : HarrisErgodic P π) (f : X → ℝ) (hf : Measurable f)
    (hgeo : GeometricallyErgodic P π) (hrev : Kernel.IsReversible P π)
    (hL2 : MemLp f 2 π) :
    SatisfiesCLT P π f := by
  have hgm : Measurable (fun x => f x - ∫ x, f x ∂π) := hf.sub_const _
  -- (a) Theorem 2(iii): the chain is exponentially ρ-mixing.
  obtain ⟨c, θ, hc, hθ, hbd⟩ := rho_mixing_exp_of_geometric_reversible P π hP hgeo hrev
  -- (b) the centred functional process inherits the mixing rate
  have hdom : ∀ n : ℕ,
      0 ≤ rhoMixingCoef (chainMeasure P π) (fun i ω => f (ω i) - ∫ x, f x ∂π) n ∧
      rhoMixingCoef (chainMeasure P π) (fun i ω => f (ω i) - ∫ x, f x ∂π) n
        ≤ rhoMixingCoef (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) n := fun n =>
    rhoMixingCoef_comp_nonneg_le_of_finite (chainMeasure P π) (fun i (ω : ℕ → X) => ω i)
      (fun x => f x - ∫ x, f x ∂π) hgm n
  -- (c) summability of the ρ coefficients
  have hgeomsum : Summable (fun n : ℕ => c * Real.exp (-θ * ((n + 1 : ℕ) : ℝ))) := by
    have hlt : |Real.exp (-θ)| < 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by linarith)
    have hs := (summable_geometric_of_abs_lt_one hlt).mul_left (c * Real.exp (-θ))
    refine hs.congr fun n => ?_
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]
    push_cast
    congr 1
    ring
  have hρ : Summable
      (fun n => rhoMixingCoef (chainMeasure P π) (fun i ω => f (ω i) - ∫ x, f x ∂π) n) := by
    rw [← summable_nat_add_iff 1]
    refine hgeomsum.of_nonneg_of_le (fun n => (hdom (n + 1)).1) (fun n => ?_)
    exact le_trans (hdom (n + 1)).2 (hbd (n + 1) (by omega))
  -- (d) stationarity and centring
  have hstat0 : IsStrictlyStationary (chainMeasure P π) (fun i (ω : ℕ → X) => ω i) :=
    isStrictlyStationary_coord_chainMeasure P π hP.1
  have hstat : IsStrictlyStationary (chainMeasure P π)
      (fun i ω => f (ω i) - ∫ x, f x ∂π) :=
    isStrictlyStationary_comp_of_measurable _ _ (fun n => measurable_pi_apply n) hstat0 _ hgm
  have hmap := map_coord_chainMeasure P π hP.1 0
  have hfint : Integrable f π := (hL2.integrable (by norm_num))
  have hmeas : AEMeasurable (fun ω : ℕ → X => ω 0) (chainMeasure P π) :=
    (measurable_pi_apply 0).aemeasurable
  have h1 : ∫ ω, f (ω 0) ∂(chainMeasure P π) = ∫ x, f x ∂π := by
    conv_rhs => rw [← hmap]
    rw [integral_map hmeas hf.aestronglyMeasurable]
  have h2 : Integrable (fun ω : ℕ → X => f (ω 0)) (chainMeasure P π) := by
    have hi : Integrable f (Measure.map (fun ω : ℕ → X => ω 0) (chainMeasure P π)) := by
      rw [hmap]; exact hfint
    exact (integrable_map_measure hf.aestronglyMeasurable hmeas).mp hi
  have hcent : ∫ ω, (f (ω 0) - ∫ x, f x ∂π) ∂(chainMeasure P π) = 0 := by
    rw [integral_sub h2 (integrable_const _), h1, integral_const]
    simp
  have hYmeas : ∀ n : ℕ, Measurable (fun ω : ℕ → X => f (ω n) - ∫ x, f x ∂π) := fun n =>
    (hf.comp (measurable_pi_apply n)).sub_const _
  have hYL2 : MemLp (fun ω : ℕ → X => f (ω 0) - ∫ x, f x ∂π) 2 (chainMeasure P π) := by
    have hm : MemLp f 2 (Measure.map (fun ω : ℕ → X => ω 0) (chainMeasure P π)) := by
      rw [hmap]; exact hL2
    exact ((memLp_map_measure_iff hf.aestronglyMeasurable hmeas).mp hm).sub (memLp_const _)
  -- (e) Theorem 7 (Ibragimov's ρ-mixing CLT) applied to the centred functional process
  have hthm7 := clt_of_summable_rho (chainMeasure P π)
    (fun i ω => f (ω i) - ∫ x, f x ∂π) hYmeas hstat hcent hYL2 hρ
  -- (f) Remark 6: transfer to every initial distribution
  exact satisfiesCLT_of_centered_functional_clt P π hP f hf hL2 hthm7.1 hthm7.2

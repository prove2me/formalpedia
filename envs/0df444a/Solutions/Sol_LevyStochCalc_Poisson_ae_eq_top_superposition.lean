-- Prove2me | solution 1 for LevyStochCalc.Poisson.ae_eq_top_superposition
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-19T08:01:05.045949+00:00
-- url     : https://prove2.me/submissions/28de8d24-a506-4e81-9432-c1839635467a

import Definitions.Def_LevyStochCalc_Poisson_PoissonSuperposition_F000

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Superposition of independent Poisson pieces

Given weights `r p ≥ 0` and probability laws `ρ p` on a measurable space `𝓧`, indexed by a
countable type, the *superposition* is the random measure `N = ∑ₚ Nₚ` where the pieces
`Nₚ = ∑_{j < Kₚ} δ_{X_{p,j}}` are independent, `Kₚ` is Poisson with mean `r p`, and the marks
`X_{p,j}` are independent with law `ρ p`. Its intensity is `Λ = ∑ₚ r p • ρ p`.

The sample space is the product `ι → ULift ℕ × (ℕ → 𝓧)` with the product law, and the
distributional facts about a single piece reduce to Poisson splitting.
-/

open MeasureTheory ProbabilityTheory Complex Filter Function Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u

section Piece

variable {𝓧 : Type u} [MeasurableSpace 𝓧]

variable {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧) [∀ p, IsProbabilityMeasure (ρ p)]

variable {r ρ}

variable (r ρ)

variable {r ρ}

variable (r ρ)

variable [Countable ι]

end Piece

section Exhaustion

end Exhaustion

section Law

variable {𝓧 : Type u} [MeasurableSpace 𝓧] {ι : Type*} (r : ι → ℝ≥0) (ρ : ι → Measure 𝓧)
  [∀ p, IsProbabilityMeasure (ρ p)]

variable {r ρ}

variable (r ρ)

variable [Countable ι]

omit [∀ p, IsProbabilityMeasure (ρ p)] [Countable ι] in
theorem AuxAT.tail (n : ℕ) :
    Tendsto (fun x : ℝ≥0 => (Po(x) : Measure ℕ) (Set.Iic n)) atTop (𝓝 0) := by
  have hset : (Set.Iic n : Set ℕ) = ↑(Finset.Iic n) := by ext; simp
  have h1 : ∀ x : ℝ≥0, (Po(x) : Measure ℕ) (Set.Iic n)
      = ∑ k ∈ Finset.Iic n, ENNReal.ofReal (Real.exp (-(x : ℝ)) * (x : ℝ) ^ k / k.factorial) := by
    intro x
    rw [hset, ← sum_measure_singleton]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [poissonMeasure_singleton]
  simp_rw [h1]
  rw [show (0 : ℝ≥0∞) = ∑ k ∈ Finset.Iic n, (0 : ℝ≥0∞) by simp]
  refine tendsto_finset_sum _ fun k _ => ?_
  rw [← ENNReal.ofReal_zero]
  refine ENNReal.tendsto_ofReal ?_
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).div_const (k.factorial : ℝ)).comp
    (NNReal.tendsto_coe_atTop.2 tendsto_id)
  simp only [zero_div] at h2
  refine h2.congr fun x => ?_
  simp only [Function.comp, id]
  ring

theorem _root_.solution {B : Set 𝓧} (hB : MeasurableSet B)
    (hinf : superIntensity r ρ B = ⊤) :
    ∀ᵐ ω ∂(superLaw r ρ), superposition ω B = ⊤ := by
  obtain ⟨F, hFm, hcof⟩ := exists_finset_exhaustion ι
  have hFt := tendsto_finset_exhaustion hFm hcof
  set lam : ℕ → ℝ≥0 := fun m => ∑ p ∈ F m, r p * (ρ p B).toNNReal with hlam_def
  have hlam : Tendsto lam atTop atTop := by
    have h1 := tendsto_sum_exhaustion hFt (fun p => (r p : ℝ≥0∞) * ρ p B)
    rw [← superIntensity_apply r ρ hB, hinf] at h1
    have h2 : (fun m => ∑ p ∈ F m, (r p : ℝ≥0∞) * ρ p B) = fun m => ((lam m : ℝ≥0) : ℝ≥0∞) := by
      funext m
      simp only [lam, ENNReal.coe_finset_sum, ENNReal.coe_mul,
        ENNReal.coe_toNNReal (measure_ne_top _ _)]
    rw [h2] at h1
    exact ENNReal.tendsto_coe_nhds_top.1 h1
  have hn : ∀ n : ℕ, superLaw r ρ {ω | superposition ω B ≤ n} = 0 := by
    intro n
    have hle : ∀ m, superLaw r ρ {ω | superposition ω B ≤ n} ≤ (Po(lam m) : Measure ℕ) (Set.Iic n) := by
      intro m
      calc superLaw r ρ {ω | superposition ω B ≤ n}
          ≤ superLaw r ρ (partialCount (F m) B ⁻¹' Set.Iic (n : ℝ)) := by
            refine measure_mono fun ω hω => ?_
            simp only [Set.mem_setOf_eq] at hω
            simp only [Set.mem_preimage, Set.mem_Iic]
            rw [partialCount_eq_toReal]
            have hs : ∑ p ∈ F m, (pieceCountOn B (ω p) : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
              refine le_trans ?_ hω
              rw [superposition_apply ω hB]
              exact ENNReal.sum_le_tsum _
            simpa using ENNReal.toReal_mono (ENNReal.natCast_ne_top n) hs
        _ = ((superLaw r ρ).map (partialCount (F m) B)) (Set.Iic (n : ℝ)) :=
            (Measure.map_apply (measurable_partialCount _ hB) measurableSet_Iic).symm
        _ = (Po(lam m) : Measure ℕ) ((Nat.cast : ℕ → ℝ) ⁻¹' Set.Iic (n : ℝ)) := by
            rw [map_partialCount r ρ _ hB, Measure.map_apply Measurable.of_discrete measurableSet_Iic]
        _ = (Po(lam m) : Measure ℕ) (Set.Iic n) := by
            congr 1; ext k; simp
    have ht := (AuxAT.tail n).comp hlam
    exact le_antisymm (ge_of_tendsto ht (Eventually.of_forall hle)) bot_le
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ n : ℕ, {ω | superposition ω B ≤ n}) (fun ω hω => ?_)
    (measure_iUnion_null hn)
  simp only [Set.mem_setOf_eq] at hω
  obtain ⟨n, hn'⟩ := ENNReal.exists_nat_gt hω
  exact Set.mem_iUnion.2 ⟨n, hn'.le⟩

end Law

end LevyStochCalc.Poisson
